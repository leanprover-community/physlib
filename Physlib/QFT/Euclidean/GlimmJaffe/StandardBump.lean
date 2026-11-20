/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Standard bump sequence

The mollifier sequence used in the OS1 endpoint condition of the Glimm–Jaffe axioms.

## i. Overview

The OS1 endpoint condition smears the two-point function with a sequence of smooth bumps
shrinking to the origin. This file fixes that sequence, following `OSforGFF`: the `n`-th bump
on `EuclideanSpace ℝ (Fin (d + 1))` has inner radius `1 / (2n)` and outer radius `1 / n`.

## ii. Key results

* `standardBumpSequence`: the standard bump sequence, defined for nonzero `n`.

## iii. Table of contents

- A. The standard bump sequence

## iv. References

* Cherkis et al., *OSforGFF*. [ref: osforgff]
-/

@[expose] public section
noncomputable section

namespace GlimmJaffe

variable {d : ℕ}

/-! ## A. The standard bump sequence -/

/-- The standard bump sequence from `OSforGFF`, with outer radius `1 / n` for nonzero `n`. -/
def standardBumpSequence (n : ℕ) (hn : n ≠ 0) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin (d + 1))) where
  rIn := 1 / (2 * n)
  rOut := 1 / n
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    exact one_div_lt_one_div_of_lt hn' (by linarith)

end GlimmJaffe
